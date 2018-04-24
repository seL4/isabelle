(*  Title:      HOL/Tools/numeral.ML
    Author:     Makarius

Logical and syntactic operations on numerals (see also HOL/Tools/hologic.ML).
*)

signature NUMERAL =
sig
  val mk_cnumber: ctyp -> int -> cterm
  val mk_number_syntax: int -> term
  val dest_num_syntax: term -> int
  val add_code: string -> (int -> int) -> (Code_Printer.literals -> int -> string) -> string -> theory -> theory
end;

structure Numeral: NUMERAL =
struct

(* numeral *)

fun dest_num_syntax (Const (@{const_syntax Num.Bit0}, _) $ t) = 2 * dest_num_syntax t
  | dest_num_syntax (Const (@{const_syntax Num.Bit1}, _) $ t) = 2 * dest_num_syntax t + 1
  | dest_num_syntax (Const (@{const_syntax Num.One}, _)) = 1;

fun mk_num_syntax n =
  if n > 0 then
    (case IntInf.quotRem (n, 2) of
      (0, 1) => Syntax.const @{const_syntax One}
    | (n, 0) => Syntax.const @{const_syntax Bit0} $ mk_num_syntax n
    | (n, 1) => Syntax.const @{const_syntax Bit1} $ mk_num_syntax n)
  else raise Match

fun mk_cbit 0 = @{cterm "Num.Bit0"}
  | mk_cbit 1 = @{cterm "Num.Bit1"}
  | mk_cbit _ = raise CTERM ("mk_cbit", []);

fun mk_cnumeral i =
  let
    fun mk 1 = @{cterm "Num.One"}
      | mk i =
      let val (q, r) = Integer.div_mod i 2 in
        Thm.apply (mk_cbit r) (mk q)
      end
  in
    if i > 0 then mk i else raise CTERM ("mk_cnumeral: negative input", [])
  end


(* number *)

local

val cterm_of = Thm.cterm_of @{context};
fun tvar S = (("'a", 0), S);

val zero_tvar = tvar @{sort zero};
val zero = cterm_of (Const (@{const_name zero_class.zero}, TVar zero_tvar));

val one_tvar = tvar @{sort one};
val one = cterm_of (Const (@{const_name one_class.one}, TVar one_tvar));

val numeral_tvar = tvar @{sort numeral};
val numeral = cterm_of (Const (@{const_name numeral}, @{typ num} --> TVar numeral_tvar));

val uminus_tvar = tvar @{sort uminus};
val uminus = cterm_of (Const (@{const_name uminus}, TVar uminus_tvar --> TVar uminus_tvar));

fun instT T v = Thm.instantiate_cterm ([(v, T)], []);

in

fun mk_cnumber T 0 = instT T zero_tvar zero
  | mk_cnumber T 1 = instT T one_tvar one
  | mk_cnumber T i =
      if i > 0 then
        Thm.apply (instT T numeral_tvar numeral) (mk_cnumeral i)
      else
        Thm.apply (instT T uminus_tvar uminus)
          (Thm.apply (instT T numeral_tvar numeral) (mk_cnumeral (~ i)));

end;

fun mk_number_syntax n =
  if n = 0 then Syntax.const @{const_syntax Groups.zero}
  else if n = 1 then Syntax.const @{const_syntax Groups.one}
  else Syntax.const @{const_syntax numeral} $ mk_num_syntax n;


(* code generator *)

local open Basic_Code_Thingol in

fun dest_num_code (IConst { sym = Code_Symbol.Constant @{const_name Num.One}, ... }) = SOME 1
  | dest_num_code (IConst { sym = Code_Symbol.Constant @{const_name Num.Bit0}, ... } `$ t) =
     (case dest_num_code t of
        SOME n => SOME (2 * n)
      | _ => NONE)
  | dest_num_code (IConst { sym = Code_Symbol.Constant @{const_name Num.Bit1}, ... } `$ t) =
     (case dest_num_code t of
        SOME n => SOME (2 * n + 1)
      | _ => NONE)
  | dest_num_code _ = NONE;

fun add_code number_of preproc print target thy =
  let
    fun pretty literals _ thm _ _ [(t, _)] =
      case dest_num_code t of
        SOME n => (Code_Printer.str o print literals o preproc) n
      | NONE => Code_Printer.eqn_error thy thm "Illegal numeral expression: illegal term";
  in
    thy |> Code_Target.set_printings (Code_Symbol.Constant (number_of,
      [(target, SOME (Code_Printer.complex_const_syntax (1, pretty)))]))
  end;

end; (*local*)

end;
