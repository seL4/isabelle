(*  Title:      FOL/ex/declIffOracle
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Example of how to declare an oracle
*)


(*New exception constructor for passing arguments to the oracle*)
exception IffOracleExn of int;

(*Internal syntactic declarations*)
val oT = Type("o",[]);

val iff = Const("op <->", [oT,oT]--->oT);

fun mk_iff 0 = Const("True", oT)
  | mk_iff n = iff $ Free("P", oT) $ mk_iff (n-1);

val Trueprop = Const("Trueprop",oT-->propT);

(*Oracle makes tautologies of the form "P <-> P <-> P <-> P <-> True"*)
fun mk_iff_oracle (sign, IffOracleExn n) = Trueprop $ mk_iff (2*n);
