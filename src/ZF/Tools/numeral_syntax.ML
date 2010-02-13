(*  Title:      ZF/Tools/numeral_syntax.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory

Concrete syntax for generic numerals.  Assumes consts and syntax of
theory Bin.
*)

signature NUMERAL_SYNTAX =
sig
  val make_binary: int -> int list
  val dest_binary: int list -> int
  val int_tr: term list -> term
  val int_tr': bool -> typ -> term list -> term
  val setup: theory -> theory
end;

structure Numeral_Syntax: NUMERAL_SYNTAX =
struct

(* bits *)

fun mk_bit 0 = Syntax.const @{const_syntax "0"}
  | mk_bit 1 = Syntax.const @{const_syntax succ} $ Syntax.const @{const_syntax 0}
  | mk_bit _ = sys_error "mk_bit";

fun dest_bit (Const (@{const_syntax "0"}, _)) = 0
  | dest_bit (Const (@{const_syntax succ}, _) $ Const (@{const_syntax "0"}, _)) = 1
  | dest_bit _ = raise Match;


(* bit strings *)

fun make_binary 0 = []
  | make_binary ~1 = [~1]
  | make_binary n = (n mod 2) :: make_binary (n div 2);

fun dest_binary [] = 0
  | dest_binary (b :: bs) = b + 2 * dest_binary bs;


(*try to handle superfluous leading digits nicely*)
fun prefix_len _ [] = 0
  | prefix_len pred (x :: xs) =
      if pred x then 1 + prefix_len pred xs else 0;

fun mk_bin i =
  let
    fun term_of [] = Syntax.const @{const_syntax Pls}
      | term_of [~1] = Syntax.const @{const_syntax Min}
      | term_of (b :: bs) = Syntax.const @{const_syntax Bit} $ term_of bs $ mk_bit b;
  in term_of (make_binary i) end;

fun bin_of (Const (@{const_syntax Pls}, _)) = []
  | bin_of (Const (@{const_syntax Min}, _)) = [~1]
  | bin_of (Const (@{const_syntax Bit}, _) $ bs $ b) = dest_bit b :: bin_of bs
  | bin_of _ = raise Match;

(*Leading 0s and (for negative numbers) -1s cause complications, though they 
  should never arise in normal use. The formalization used in HOL prevents 
  them altogether.*)
fun show_int t =
  let
    val rev_digs = bin_of t;
    val (sign, zs) =
      (case rev rev_digs of
         ~1 :: bs => ("-", prefix_len (equal 1) bs)
      | bs => ("",  prefix_len (equal 0) bs));
    val num = string_of_int (abs (dest_binary rev_digs));
  in
    "#" ^ sign ^ implode (replicate zs "0") ^ num
  end;


(* translation of integer constant tokens to and from binary *)

fun int_tr (*"_Int"*) [t as Free (str, _)] =
      Syntax.const @{const_syntax integ_of} $ mk_bin (#value (Syntax.read_xnum str))
  | int_tr (*"_Int"*) ts = raise TERM ("int_tr", ts);

fun int_tr' _ _ (*"integ_of"*) [t] =
      Syntax.const @{syntax_const "_Int"} $ Syntax.free (show_int t)
  | int_tr' (_: bool) (_: typ) _ = raise Match;


val setup =
 (Sign.add_trfuns ([], [(@{syntax_const "_Int"}, int_tr)], [], []) #>
  Sign.add_trfunsT [(@{const_syntax integ_of}, int_tr')]);

end;
