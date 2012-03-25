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
val zeroT = Thm.ctyp_of_term zero;

val one = @{cpat "1"};
val oneT = Thm.ctyp_of_term one;

val numeral = @{cpat "numeral"};
val numeralT = Thm.ctyp_of @{theory} (Term.range_type (Thm.typ_of (Thm.ctyp_of_term numeral)));

val neg_numeral = @{cpat "neg_numeral"};
val neg_numeralT = Thm.ctyp_of @{theory} (Term.range_type (Thm.typ_of (Thm.ctyp_of_term neg_numeral)));

fun instT T V = Thm.instantiate_cterm ([(V, T)], []);

in

fun mk_cnumber T 0 = instT T zeroT zero
  | mk_cnumber T 1 = instT T oneT one
  | mk_cnumber T i =
    if i > 0 then Thm.apply (instT T numeralT numeral) (mk_cnumeral i)
    else Thm.apply (instT T neg_numeralT neg_numeral) (mk_cnumeral (~i));

end;


(* code generator *)

local open Basic_Code_Thingol in

fun add_code number_of negative print target thy =
  let
    fun dest_numeral one' bit0' bit1' thm t =
      let
        fun dest_bit (IConst (c, _)) = if c = bit0' then 0
              else if c = bit1' then 1
              else Code_Printer.eqn_error thm "Illegal numeral expression: illegal bit"
          | dest_bit _ = Code_Printer.eqn_error thm "Illegal numeral expression: illegal bit";
        fun dest_num (IConst (c, _)) = if c = one' then 1
              else Code_Printer.eqn_error thm "Illegal numeral expression: illegal leading digit"
          | dest_num (t1 `$ t2) = 2 * dest_num t2 + dest_bit t1
          | dest_num _ = Code_Printer.eqn_error thm "Illegal numeral expression: illegal term";
      in if negative then ~ (dest_num t) else dest_num t end;
    fun pretty literals [one', bit0', bit1'] _ thm _ _ [(t, _)] =
      (Code_Printer.str o print literals o dest_numeral one' bit0' bit1' thm) t;
  in
    thy |> Code_Target.add_const_syntax target number_of
      (SOME (Code_Printer.complex_const_syntax (1, ([@{const_name Num.One},
        @{const_name Num.Bit0}, @{const_name Num.Bit1}], pretty))))
  end;

end; (*local*)

end;
