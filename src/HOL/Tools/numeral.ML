(*  Title:      HOL/Tools/numeral.ML
    ID:         $Id$
    Author:     Makarius

Logical operations on numerals (see also HOL/hologic.ML).
*)

signature NUMERAL =
sig
  val mk_cnumeral: int -> cterm
  val mk_cnumber: ctyp -> int -> cterm
  val add_code: string -> bool -> bool -> string -> theory -> theory
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
        Thm.capply (mk_cbit r) (mk_cnumeral q)
      end;


(* number *)

local

val zero = @{cpat "0"};
val zeroT = Thm.ctyp_of_term zero;

val one = @{cpat "1"};
val oneT = Thm.ctyp_of_term one;

val number_of = @{cpat "number_of"};
val numberT = Thm.ctyp_of (the_context ()) (Term.range_type (Thm.typ_of (Thm.ctyp_of_term number_of)));

fun instT T V = Thm.instantiate_cterm ([(V, T)], []);

in

fun mk_cnumber T 0 = instT T zeroT zero
  | mk_cnumber T 1 = instT T oneT one
  | mk_cnumber T i = Thm.capply (instT T numberT number_of) (mk_cnumeral i);

end;


(* code generator *)

local open Basic_Code_Thingol in

fun add_code number_of negative unbounded target thy =
  let
    val pls' = Code_Name.const thy @{const_name Int.Pls};
    val min' = Code_Name.const thy @{const_name Int.Min};
    val bit0' = Code_Name.const thy @{const_name Int.Bit0};
    val bit1' = Code_Name.const thy @{const_name Int.Bit1};
    val pr_numeral = (Code_Printer.literal_numeral o Code_Target.the_literals thy) target;
    fun dest_bit thm (IConst (c, _)) = if c = bit0' then 0
          else if c = bit1' then 1
          else Code_Printer.nerror thm "Illegal numeral expression: illegal bit"
      | dest_bit thm _ = Code_Printer.nerror thm "Illegal numeral expression: illegal bit";
    fun dest_numeral thm (IConst (c, _)) = if c = pls' then SOME 0
          else if c = min' then
            if negative then SOME ~1 else NONE
          else Code_Printer.nerror thm "Illegal numeral expression: illegal leading digit"
      | dest_numeral thm (t1 `$ t2) =
          let val (n, b) = (dest_numeral thm t2, dest_bit thm t1)
          in case n of SOME n => SOME (2 * n + b) | NONE => NONE end
      | dest_numeral thm _ = Code_Printer.nerror thm "Illegal numeral expression: illegal term";
    fun pretty _ thm _ _ _ [(t, _)] =
      (Code_Printer.str o pr_numeral unbounded o the_default 0 o dest_numeral thm) t;
  in
    thy
    |> Code_Target.add_syntax_const target number_of (SOME (1, pretty))
  end;

end; (*local*)

end;
