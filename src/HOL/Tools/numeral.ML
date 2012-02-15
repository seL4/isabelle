(*  Title:      HOL/Tools/numeral.ML
    Author:     Makarius

Logical operations on numerals (see also HOL/hologic.ML).
*)

signature NUMERAL =
sig
  val mk_cnumeral: int -> cterm
  val mk_cnumber: ctyp -> int -> cterm
  val add_code: string -> bool -> (Code_Printer.literals -> int -> string) -> string -> theory -> theory
end;

structure Numeral: NUMERAL =
struct

(* numeral *)

fun mk_cbit 0 = @{cterm "Int.Bit0"}
  | mk_cbit 1 = @{cterm "Int.Bit1"}
  | mk_cbit _ = raise CTERM ("mk_cbit", []);

fun mk_cnumeral 0 = @{cterm "Int.Pls"}
  | mk_cnumeral ~1 = @{cterm "Int.Min"}
  | mk_cnumeral i =
      let val (q, r) = Integer.div_mod i 2 in
        Thm.apply (mk_cbit r) (mk_cnumeral q)
      end;


(* number *)

local

val zero = @{cpat "0"};
val zeroT = Thm.ctyp_of_term zero;

val one = @{cpat "1"};
val oneT = Thm.ctyp_of_term one;

val number_of = @{cpat "number_of"};
val numberT = Thm.ctyp_of @{theory} (Term.range_type (Thm.typ_of (Thm.ctyp_of_term number_of)));

fun instT T V = Thm.instantiate_cterm ([(V, T)], []);

in

fun mk_cnumber T 0 = instT T zeroT zero
  | mk_cnumber T 1 = instT T oneT one
  | mk_cnumber T i = Thm.apply (instT T numberT number_of) (mk_cnumeral i);

end;


(* code generator *)

local open Basic_Code_Thingol in

fun add_code number_of negative print target thy =
  let
    fun dest_numeral pls' min' bit0' bit1' thm =
      let
        fun dest_bit (IConst (c, _)) = if c = bit0' then 0
              else if c = bit1' then 1
              else Code_Printer.eqn_error thm "Illegal numeral expression: illegal bit"
          | dest_bit _ = Code_Printer.eqn_error thm "Illegal numeral expression: illegal bit";
        fun dest_num (IConst (c, _)) = if c = pls' then SOME 0
              else if c = min' then
                if negative then SOME ~1 else NONE
              else Code_Printer.eqn_error thm "Illegal numeral expression: illegal leading digit"
          | dest_num (t1 `$ t2) =
              let val (n, b) = (dest_num t2, dest_bit t1)
              in case n of SOME n => SOME (2 * n + b) | NONE => NONE end
          | dest_num _ = Code_Printer.eqn_error thm "Illegal numeral expression: illegal term";
      in dest_num end;
    fun pretty literals [pls', min', bit0', bit1'] _ thm _ _ [(t, _)] =
      (Code_Printer.str o print literals o the_default 0 o dest_numeral pls' min' bit0' bit1' thm) t;
  in
    thy |> Code_Target.add_const_syntax target number_of
      (SOME (Code_Printer.complex_const_syntax (1, ([@{const_name Int.Pls}, @{const_name Int.Min},
        @{const_name Int.Bit0}, @{const_name Int.Bit1}], pretty))))
  end;

end; (*local*)

end;
