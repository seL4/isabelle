(*  Title:      HOL/Tools/numeral_syntax.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Concrete syntax for generic numerals.  Assumes consts and syntax of
theory HOL/Numeral.
*)

signature NUMERAL_SYNTAX =
sig
  val setup: (theory -> theory) list
end;

structure NumeralSyntax: NUMERAL_SYNTAX =
struct


(* bits *)

fun dest_bit (Const ("False", _)) = 0
  | dest_bit (Const ("True", _)) = 1
  | dest_bit _ = raise Match;


(* bit strings *)   (*we try to handle superfluous leading digits nicely*)

fun prefix_len _ [] = 0
  | prefix_len pred (x :: xs) =
      if pred x then 1 + prefix_len pred xs else 0;

fun bin_of (Const ("bin.Pls", _)) = []
  | bin_of (Const ("bin.Min", _)) = [~1]
  | bin_of (Const ("Bit", _) $ bs $ b) = dest_bit b :: bin_of bs
  | bin_of _ = raise Match;

val dest_bin = HOLogic.int_of o bin_of;

fun dest_bin_str tm =
  let
    val rev_digs = bin_of tm;
    val (sign, zs) =
      (case rev rev_digs of
        ~1 :: bs => ("-", prefix_len (equal 1) bs)
      | bs => ("", prefix_len (equal 0) bs));
    val i = HOLogic.int_of rev_digs;
    val num = string_of_int (abs i);
  in
    if i = 0 orelse i = 1 then raise Match
    else sign ^ implode (replicate zs "0") ^ num
  end;


(* translation of integer numeral tokens to and from bitstrings *)

fun numeral_tr (*"_Numeral"*) [t as Const (str, _)] =
      (Syntax.const "Numeral.number_of" $ HOLogic.mk_bin (Syntax.read_xnum str))
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
 [Theory.hide_consts false ["Numeral.bin.Pls", "Numeral.bin.Min"],
  Theory.add_trfuns ([], [("_Numeral", numeral_tr)], [], []),
  Theory.add_trfunsT [("number_of", numeral_tr'), ("Numeral.number_of", numeral_tr')]];


end;
