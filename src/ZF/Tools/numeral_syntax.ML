(*  Title:      ZF/Tools/numeral_syntax.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory

Concrete syntax for generic numerals.  Assumes consts and syntax of
theory ZF/Integ/Bin.
*)

signature NUMERAL_SYNTAX =
sig
  val dest_bin : term -> int
  val mk_bin   : int -> term
  val int_tr   : term list -> term
  val int_tr'  : bool -> typ -> term list -> term
  val setup    : (theory -> theory) list
end;

structure NumeralSyntax: NUMERAL_SYNTAX =
struct

open Syntax;

(* Bits *)

val zero = Const("0", iT);
val succ = Const("succ", iT --> iT);

fun mk_bit 0 = zero
  | mk_bit 1 = succ$zero
  | mk_bit _ = sys_error "mk_bit";

fun dest_bit (Const ("0", _)) = 0
  | dest_bit (Const ("succ", _) $ Const ("0", _)) = 1
  | dest_bit _ = raise Match;


(* Bit strings *)   (*we try to handle superfluous leading digits nicely*)

fun prefix_len _ [] = 0
  | prefix_len pred (x :: xs) =
      if pred x then 1 + prefix_len pred xs else 0;

fun scan_int str =
  let val (sign, digs) =
       (case Symbol.explode str of
	 "#" :: "-" :: cs => (~1, cs)
       | "#" :: cs => (1, cs)
       | _ => raise ERROR);

  in  sign * (#1 (read_int digs))  end;


val pls_const = Const ("Bin.bin.Pls", iT)
and min_const = Const ("Bin.bin.Min", iT)
and bit_const = Const ("Bin.bin.Bit", [iT, iT] ---> iT);

fun mk_bin i =
  let fun bin_of 0  = []
	| bin_of ~1 = [~1]
	| bin_of n  = (n mod 2) :: bin_of (n div 2);

      fun term_of []   = pls_const
	| term_of [~1] = min_const
	| term_of (b :: bs) = bit_const $ term_of bs $ mk_bit b;
  in
    term_of (bin_of i)
  end;

(*we consider all "spellings", since they could vary depending on the caller*)
fun bin_of (Const ("Pls", _)) = []
  | bin_of (Const ("bin.Pls", _)) = []
  | bin_of (Const ("Bin.bin.Pls", _)) = []
  | bin_of (Const ("Min", _)) = [~1]
  | bin_of (Const ("bin.Min", _)) = [~1]
  | bin_of (Const ("Bin.bin.Min", _)) = [~1]
  | bin_of (Const ("Bit", _) $ bs $ b) = dest_bit b :: bin_of bs
  | bin_of (Const ("bin.Bit", _) $ bs $ b) = dest_bit b :: bin_of bs
  | bin_of (Const ("Bin.bin.Bit", _) $ bs $ b) = dest_bit b :: bin_of bs
  | bin_of _ = raise Match;

fun integ_of [] = 0
  | integ_of (b :: bs) = b + 2 * integ_of bs;

val dest_bin = integ_of o bin_of;

(*leading 0s and (for negative numbers) -1s cause complications,
  though they should never arise in normal use.*)
fun show_int t =
  let
    val rev_digs = bin_of t;
    val (sign, zs) =
	(case rev rev_digs of
	     ~1 :: bs => ("-", prefix_len (equal 1) bs)
	   | bs =>       ("",  prefix_len (equal 0) bs));
    val num = string_of_int (abs (integ_of rev_digs));
  in
    "#" ^ sign ^ implode (replicate zs "0") ^ num
  end;



(* translation of integer constant tokens to and from binary *)

fun int_tr (*"_Int"*) [t as Free (str, _)] =
      (const "integ_of" $
	(mk_bin (scan_int str) handle ERROR => raise TERM ("int_tr", [t])))
  | int_tr (*"_Int"*) ts = raise TERM ("int_tr", ts);

fun int_tr' _ _ (*"integ_of"*) [t] = const "_Int" $ free (show_int t)
  | int_tr' (_:bool) (_:typ)     _ = raise Match;


val setup =
 [Theory.add_trfuns ([], [("_Int", int_tr)], [], []),
  Theory.add_trfunsT [("integ_of", int_tr'), ("Bin.integ_of", int_tr')]];

end;
