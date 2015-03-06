(*  Title:      HOL/Tools/numeral.ML
    Author:     Makarius

Logical operations on numerals (see also HOL/Tools/hologic.ML).
*)

signature NUMERAL =
sig
  val mk_cnumeral: int -> cterm
  val mk_cnumber: ctyp -> int -> cterm
  val mk_number_syntax: int -> term
  val add_code: string -> (int -> int) -> (Code_Printer.literals -> int -> string) -> string -> theory -> theory
end;

structure Numeral: NUMERAL =
struct

(* numeral *)

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

val zero = @{cpat "0"};
val zeroT = Thm.ctyp_of_cterm zero;

val one = @{cpat "1"};
val oneT = Thm.ctyp_of_cterm one;

val numeral = @{cpat "numeral"};
val numeralT = Thm.ctyp_of @{context} (Term.range_type (Thm.typ_of_cterm numeral));

val uminus = @{cpat "uminus"};
val uminusT = Thm.ctyp_of @{context} (Term.range_type (Thm.typ_of_cterm uminus));

fun instT T V = Thm.instantiate_cterm ([(V, T)], []);

in

fun mk_cnumber T 0 = instT T zeroT zero
  | mk_cnumber T 1 = instT T oneT one
  | mk_cnumber T i =
    if i > 0 then Thm.apply (instT T numeralT numeral) (mk_cnumeral i)
    else Thm.apply (instT T uminusT uminus) (Thm.apply (instT T numeralT numeral) (mk_cnumeral (~i)));

end;

fun mk_num_syntax n =
  if n > 0 then
    (case IntInf.quotRem (n, 2) of
      (0, 1) => Syntax.const @{const_syntax One}
    | (n, 0) => Syntax.const @{const_syntax Bit0} $ mk_num_syntax n
    | (n, 1) => Syntax.const @{const_syntax Bit1} $ mk_num_syntax n)
  else raise Match

fun mk_number_syntax n =
  if n = 0 then Syntax.const @{const_syntax Groups.zero}
  else if n = 1 then Syntax.const @{const_syntax Groups.one}
  else Syntax.const @{const_syntax numeral} $ mk_num_syntax n;


(* code generator *)

local open Basic_Code_Thingol in

fun add_code number_of preproc print target thy =
  let
    fun pretty literals _ thm _ _ [(t, _)] =
      let
        fun dest_bit (IConst { sym = Code_Symbol.Constant @{const_name Num.Bit0}, ... }) = 0
          | dest_bit (IConst { sym = Code_Symbol.Constant @{const_name Num.Bit1}, ... }) = 1
          | dest_bit _ = Code_Printer.eqn_error thy thm "Illegal numeral expression: illegal bit";
        fun dest_num (IConst { sym = Code_Symbol.Constant @{const_name Num.One}, ... }) = 1
          | dest_num (t1 `$ t2) = 2 * dest_num t2 + dest_bit t1
          | dest_num _ = Code_Printer.eqn_error thy thm "Illegal numeral expression: illegal term";
      in (Code_Printer.str o print literals o preproc o dest_num) t end;
  in
    thy |> Code_Target.set_printings (Code_Symbol.Constant (number_of,
      [(target, SOME (Code_Printer.complex_const_syntax (1, pretty)))]))
  end;

end; (*local*)

end;
