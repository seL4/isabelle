(*  Title:      ZF/Tools/numeral_syntax.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory

Concrete syntax for generic numerals.
*)

signature NUMERAL_SYNTAX =
sig
  val make_binary: int -> int list
  val dest_binary: int list -> int
end;

structure Numeral_Syntax: NUMERAL_SYNTAX =
struct

(* bits *)

fun mk_bit 0 = Syntax.const @{const_syntax zero}
  | mk_bit 1 = Syntax.const @{const_syntax succ} $ Syntax.const @{const_syntax zero}
  | mk_bit _ = raise Fail "mk_bit";

fun dest_bit (Const (@{const_syntax zero}, _)) = 0
  | dest_bit (Const (@{const_syntax one}, _)) = 1
  | dest_bit (Const (@{const_syntax succ}, _) $ Const (@{const_syntax zero}, _)) = 1
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
    val (c, zs) =
      (case rev rev_digs of
         ~1 :: bs => (@{syntax_const "_Neg_Int"}, prefix_len (equal 1) bs)
      | bs => (@{syntax_const "_Int"},  prefix_len (equal 0) bs));
    val num = string_of_int (abs (dest_binary rev_digs));
  in (c, implode (replicate zs "0") ^ num) end;


(* translation of integer constant tokens to and from binary *)

fun int_tr [Free (s, _)] =
      Syntax.const @{const_syntax integ_of} $ mk_bin (#value (Lexicon.read_num s))
  | int_tr ts = raise TERM ("int_tr", ts);

fun neg_int_tr [Free (s, _)] =
      Syntax.const @{const_syntax integ_of} $ mk_bin (~ (#value (Lexicon.read_num s)))
  | neg_int_tr ts = raise TERM ("neg_int_tr", ts);

fun integ_of_tr' [t] =
      let val (c, s) = show_int t
      in Syntax.const c $ Syntax.free s end
  | integ_of_tr' _ = raise Match;

val _ = Theory.setup
 (Sign.parse_translation
   [(@{syntax_const "_Int"}, K int_tr),
    (@{syntax_const "_Neg_Int"}, K neg_int_tr)] #>
  Sign.print_translation
   [(@{const_syntax integ_of}, K integ_of_tr')]);

end;
