(*  Title:      HOL/Tools/Int.ML
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
val numberT = Thm.ctyp_of @{theory} (Term.range_type (Thm.typ_of (Thm.ctyp_of_term number_of)));

fun instT T V = Thm.instantiate_cterm ([(V, T)], []);

in

fun mk_cnumber T 0 = instT T zeroT zero
  | mk_cnumber T 1 = instT T oneT one
  | mk_cnumber T i = Thm.capply (instT T numberT number_of) (mk_cnumeral i);

end;


(* code generator *)

fun add_code number_of negative unbounded target =
  Code_Target.add_pretty_numeral target negative unbounded number_of
  @{const_name Int.Pls} @{const_name Int.Min}
  @{const_name Int.Bit0} @{const_name Int.Bit1};

end;
