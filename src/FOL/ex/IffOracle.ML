(*  Title:      FOL/ex/IffOracle.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Example of how to use an oracle
*)

fun iff_oracle n =
  invoke_oracle IffOracle.thy "iff" (Theory.sign_of IffOracle.thy, IffOracleExn n);


iff_oracle 2;
iff_oracle 10;
#der(rep_thm it);

(*These oracle calls had better fail*)

(iff_oracle 5; raise ERROR)
  handle IffOracleExn _ => writeln"Failed, as expected";

(iff_oracle 0; raise ERROR)
  handle IffOracleExn _ => writeln"Failed, as expected";  
