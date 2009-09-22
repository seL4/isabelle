(*  ID:         $Id$
    Authors:    Tobias Nipkow, TU Muenchen

Concrete syntax for floats
*)

signature FLOAT_SYNTAX =
sig
  val setup: theory -> theory
end;

structure FloatSyntax: FLOAT_SYNTAX =
struct

(* parse translation *)

local

fun mk_number i =
  let
    fun mk 0 = Syntax.const @{const_name Int.Pls}
      | mk ~1 =  Syntax.const @{const_name Int.Min}
      | mk i = let val (q, r) = Integer.div_mod i 2
               in HOLogic.mk_bit r $ (mk q) end;
  in Syntax.const @{const_name Int.number_of} $ mk i end;

fun mk_frac str =
  let
    val {mant=i, exp = n} = Syntax.read_float str;
    val exp = Syntax.const @{const_name Power.power};
    val ten = mk_number 10;
    val exp10 = if n=1 then ten else exp $ ten $ (mk_number n);
  in (Syntax.const @{const_name divide}) $ (mk_number i) $ exp10 end
in

fun float_tr (*"_Float"*) [t as Const (str, _)] = mk_frac str
  | float_tr (*"_Float"*) ts = raise TERM ("float_tr", ts);

end;


(* theory setup *)

val setup =
  Sign.add_trfuns ([], [("_Float", float_tr)], [], []);

end;
