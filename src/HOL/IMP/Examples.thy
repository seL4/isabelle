(*  Title:      HOL/IMP/Examples.thy
    ID:         $Id$
    Author:     David von Oheimb, TUM
    Copyright   2000 TUM
*)

Examples = Natural +

defs (* bring up the deferred definition for update *)

 update_def "update == fun_upd"

constdefs
  
  factorial :: loc => loc => com
 "factorial a b == b :== (%s. 1);
               WHILE (%s. s a ~= 0) DO
                 (b :== (%s. s b * s a); a :== (%s. s a - 1))"
  
end
