(*  Title:      ZF/Tools/numeral_syntax.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory

Concrete syntax for generic numerals.  Assumes consts and syntax of
theory Bin.
*)

signature NUMERAL_SYNTAX =
sig
  val dest_bin : term -> int
  val mk_bin   : int -> term
  val int_tr   : term list -> term
  val int_tr'  : bool -> typ -> term list -> term
  val setup    : theory -> theory
end;

structure NumeralSyntax: NUMERAL_SYNTAX =
struct

(* Bits *)

fun mk_bit 0 = @{term "0"}
  | mk_bit 1 = @{term "succ(0)"}
  | mk_bit _ = sys_error "mk_bit";

fun dest_bit (Const (@{const_name "0"}, _)) = 0
  | dest_bit (Const (@{const_name succ}, _) $ Const (@{const_name "0"}, _)) = 1
  | dest_bit _ = raise Match;


(* Bit strings *)   (*we try to handle superfluous leading digits nicely*)

fun prefix_len _ [] = 0
  | prefix_len pred (x :: xs) =
      if pred x then 1 + prefix_len pred xs else 0;

fun mk_bin i =
  let fun bin_of_int 0  = []
        | bin_of_int ~1 = [~1]
        | bin_of_int n  = (n mod 2) :: bin_of_int (n div 2);

      fun term_of [] = @{const Pls}
            | term_of [~1] = @{const Min}
            | term_of (b :: bs) = @{const Bit} $ term_of bs $ mk_bit b;
  in
    term_of (bin_of_int i)
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

(*Convert a list of bits to an integer*)
fun integ_of [] = 0
  | integ_of (b :: bs) = b + 2 * integ_of bs;

val dest_bin = integ_of o bin_of;

(*leading 0s and (for negative numbers) -1s cause complications, though they 
  should never arise in normal use. The formalization used in HOL prevents 
  them altogether.*)
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
      Syntax.const "integ_of" $ mk_bin (#value (Syntax.read_xnum str))
  | int_tr (*"_Int"*) ts = raise TERM ("int_tr", ts);

fun int_tr' _ _ (*"integ_of"*) [t] = Syntax.const "_Int" $ Syntax.free (show_int t)
  | int_tr' (_:bool) (_:typ)     _ = raise Match;


val setup =
 (Sign.add_trfuns ([], [("_Int", int_tr)], [], []) #>
  Sign.add_trfunsT [("integ_of", int_tr'), ("Bin.integ_of", int_tr')]);

end;
