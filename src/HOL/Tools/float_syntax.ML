(*  Title:      HOL/Tools/float_syntax.ML
    Author:     Tobias Nipkow, TU Muenchen

Concrete syntax for floats.
*)

signature FLOAT_SYNTAX =
sig
  val setup: theory -> theory
end;

structure Float_Syntax: FLOAT_SYNTAX =
struct

(* parse translation *)

local

fun mk_number i =
  let
    fun mk 1 = Syntax.const @{const_syntax Num.One}
      | mk i =
          let val (q, r) = Integer.div_mod i 2
          in HOLogic.mk_bit r $ (mk q) end;
  in
    if i = 0 then Syntax.const @{const_syntax Groups.zero}
    else if i > 0 then Syntax.const @{const_syntax Num.numeral} $ mk i
    else Syntax.const @{const_syntax Num.neg_numeral} $ mk (~i)
  end;

fun mk_frac str =
  let
    val {mant = i, exp = n} = Lexicon.read_float str;
    val exp = Syntax.const @{const_syntax Power.power};
    val ten = mk_number 10;
    val exp10 = if n = 1 then ten else exp $ ten $ mk_number n;
  in Syntax.const @{const_syntax divide} $ mk_number i $ exp10 end;

in

fun float_tr [(c as Const (@{syntax_const "_constrain"}, _)) $ t $ u] = c $ float_tr [t] $ u
  | float_tr [t as Const (str, _)] = mk_frac str
  | float_tr ts = raise TERM ("float_tr", ts);

end;


(* theory setup *)

val setup =
  Sign.add_trfuns ([], [(@{syntax_const "_Float"}, float_tr)], [], []);

end;
