(*  Title:      HOL/Tools/numeral_syntax.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Concrete syntax for generic numerals.  Assumes consts and syntax of
theory HOL/Numeral.
*)

signature NUMERAL_SYNTAX =
sig
  val dest_bin : term -> int
  val mk_bin   : int -> term
  val setup    : (theory -> theory) list
end;

structure NumeralSyntax: NUMERAL_SYNTAX =
struct


(* bits *)

fun mk_bit 0 = HOLogic.false_const
  | mk_bit 1 = HOLogic.true_const
  | mk_bit _ = sys_error "mk_bit";

fun dest_bit (Const ("False", _)) = 0
  | dest_bit (Const ("True", _)) = 1
  | dest_bit _ = raise Match;


(* bit strings *)   (*we try to handle superfluous leading digits nicely*)

fun prefix_len _ [] = 0
  | prefix_len pred (x :: xs) =
      if pred x then 1 + prefix_len pred xs else 0;

fun mk_bin n =
  let
    fun bin_of 0  = []
      | bin_of ~1 = [~1]
      | bin_of n  = (n mod 2) :: bin_of (n div 2);

    fun term_of []   = HOLogic.pls_const
      | term_of [~1] = HOLogic.min_const
      | term_of (b :: bs) = HOLogic.bit_const $ term_of bs $ mk_bit b;
    in term_of (bin_of n) end;

(*we consider all "spellings"; Min is likely to be declared elsewhere*)
fun bin_of (Const ("Pls", _)) = []
  | bin_of (Const ("bin.Pls", _)) = []
  | bin_of (Const ("Numeral.bin.Pls", _)) = []
  | bin_of (Const ("Min", _)) = [~1]
  | bin_of (Const ("bin.Min", _)) = [~1]
  | bin_of (Const ("Numeral.bin.Min", _)) = [~1]
  | bin_of (Const ("Bit", _) $ bs $ b) = dest_bit b :: bin_of bs
  | bin_of (Const ("bin.Bit", _) $ bs $ b) = dest_bit b :: bin_of bs
  | bin_of (Const ("Numeral.bin.Bit", _) $ bs $ b) = dest_bit b :: bin_of bs
  | bin_of _ = raise Match;

val dest_bin = HOLogic.int_of o bin_of;

fun dest_bin_str tm =
  let
    val rev_digs = bin_of tm;
    val (sign, zs) =
      (case rev rev_digs of
        ~1 :: bs => ("-", prefix_len (equal 1) bs)
      | bs => ("", prefix_len (equal 0) bs));
    val num = string_of_int (abs (HOLogic.int_of rev_digs));
  in "#" ^ sign ^ implode (replicate zs "0") ^ num end;


(* translation of integer numeral tokens to and from bitstrings *)

fun numeral_tr (*"_Numeral"*) [t as Free (str, _)] =
      (Syntax.const "Numeral.number_of" $ mk_bin (Syntax.read_xnum str))
  | numeral_tr (*"_Numeral"*) ts = raise TERM ("numeral_tr", ts);

fun numeral_tr' show_sorts (*"number_of"*) (Type ("fun", [_, T])) (t :: ts) =
      let val t' = Syntax.const "_Numeral" $ (Syntax.const "_xnum" $ Syntax.free (dest_bin_str t)) in
        if not (! show_types) andalso can Term.dest_Type T then t'
        else Syntax.const Syntax.constrainC $ t' $ Syntax.term_of_typ show_sorts T
      end
  | numeral_tr' _ (*"number_of"*) _ _ = raise Match;


(* theory setup *)

val setup =
 [Theory.add_trfuns ([], [("_Numeral", numeral_tr)], [], []),
  Theory.add_trfunsT [("number_of", numeral_tr'), ("Numeral.number_of", numeral_tr')]];


end;
