(*  Title:      HOL/Tools/numeral_syntax.ML
    ID:         $Id$
    Authors:    Markus Wenzel, TU Muenchen

Concrete syntax for generic numerals -- preserves leading zeros/ones.
*)

signature NUMERAL_SYNTAX =
sig
  val setup: theory -> theory
end;

structure NumeralSyntax: NUMERAL_SYNTAX =
struct


(* parse translation *)

local

fun mk_bin num =
  let
    val {leading_zeros = z, value, ...} = Syntax.read_xnum num;
    fun bit b bs = Syntax.const "\\<^const>Numeral.Bit" $ bs $ HOLogic.mk_bit b;
    fun mk 0 = (* FIXME funpow z (bit 0) *) (Syntax.const "\\<^const>Numeral.Pls")
      | mk ~1 = (* FIXME funpow z (bit 1) *) (Syntax.const "\\<^const>Numeral.Min")
      | mk i = let val (q, r) = IntInf.divMod (i, 2) in bit (IntInf.toInt r) (mk q) end;
  in mk value end;

in

fun numeral_tr (*"_Numeral"*) [t as Const (num, _)] =
      Syntax.const "Numeral.number_of" $ mk_bin num
  | numeral_tr (*"_Numeral"*) ts = raise TERM ("numeral_tr", ts);

end;


(* print translation *)

local

fun dest_bit (Const ("Numeral.bit.B0", _)) = 0
  | dest_bit (Const ("Numeral.bit.B1", _)) = 1
  | dest_bit (Const ("bit.B0", _)) = 0
  | dest_bit (Const ("bit.B1", _)) = 1
  | dest_bit _ = raise Match;

fun dest_bin (Const ("\\<^const>Numeral.Pls", _)) = []
  | dest_bin (Const ("\\<^const>Numeral.Min", _)) = [~1]
  | dest_bin (Const ("\\<^const>Numeral.Bit", _) $ bs $ b) = dest_bit b :: dest_bin bs
  | dest_bin _ = raise Match;

fun leading _ [] = 0
  | leading (i: int) (j :: js) = if i = j then 1 + leading i js else 0;

fun int_of [] = 0
  | int_of (b :: bs) = IntInf.fromInt b + 2 * int_of bs;

fun dest_bin_str tm =
  let
    val rev_digs = dest_bin tm;
    val (sign, z) =
      (case rev rev_digs of
        ~1 :: bs => ("-", leading 1 bs)
      | bs => ("", leading 0 bs));
    val i = int_of rev_digs;
    val num = IntInf.toString (IntInf.abs i);
  in
    if (i = 0 orelse i = 1) andalso z = 0 then raise Match
    else sign ^ implode (replicate z "0") ^ num
  end;

in

fun numeral_tr' show_sorts (*"number_of"*) (Type ("fun", [_, T])) (t :: ts) =
      let val t' = Syntax.const "_Numeral" $ Syntax.free (dest_bin_str t) in
        if not (! show_types) andalso can Term.dest_Type T then t'
        else Syntax.const Syntax.constrainC $ t' $ Syntax.term_of_typ show_sorts T
      end
  | numeral_tr' _ (*"number_of"*) T (t :: ts) =
      if T = dummyT then Syntax.const "_Numeral" $ Syntax.free (dest_bin_str t)
      else raise Match
  | numeral_tr' _ (*"number_of"*) _ _ = raise Match;

end;


(* theory setup *)

val setup =
  Theory.add_trfuns ([], [("_Numeral", numeral_tr)], [], []) #>
  Theory.add_trfunsT [("number_of", numeral_tr'), ("Numeral.number_of", numeral_tr')];

end;
