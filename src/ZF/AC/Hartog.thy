(*  Title: 	ZF/AC/Hartog.thy
    ID:         $Id$
    Author: 	Krzysztof Grabczewski

Hartog's function.
*)

Hartog = Cardinal +

consts

  Hartog :: i => i

defs

  Hartog_def "Hartog(X) == LEAST i. ~i lepoll X"

end
