(*  Title:      FOL/ex/IffOracle.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge
*)

header{*Example of Declaring an Oracle*}

theory IffOracle imports FOL begin

text{*This oracle makes tautologies of the form "P <-> P <-> P <-> P".
The length is specified by an integer, which is checked to be even and 
positive.*}

ML
{*
local

(* internal syntactic declarations *)

val oT = Type("o",[]);

val iff = Const("op <->", [oT,oT]--->oT);

fun mk_iff 1 = Free("P", oT)
  | mk_iff n = iff $ Free("P", oT) $ mk_iff (n-1);

val Trueprop = Const("Trueprop",oT-->propT);

in

(*new exception constructor for passing arguments to the oracle*)
exception IffOracleExn of int;

fun mk_iff_oracle (sign, IffOracleExn n) =
  if n > 0 andalso n mod 2 = 0
  then Trueprop $ mk_iff n
  else raise IffOracleExn n;

end
*}

oracle
  iff = mk_iff_oracle

end


