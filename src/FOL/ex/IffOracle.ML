(*  Title:      FOL/ex/IffOracle
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Example of how to use an oracle
*)

invoke_oracle (IffOracle.thy, sign_of IffOracle.thy, IffOracleExn 0);
invoke_oracle (IffOracle.thy, sign_of IffOracle.thy, IffOracleExn 5);
invoke_oracle (IffOracle.thy, sign_of IffOracle.thy, IffOracleExn 10);
#der(rep_thm it);

