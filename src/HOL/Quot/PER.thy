(*  Title:      HOL/Quot/PER.thy
    ID:         $Id$
    Author:     Oscar Slotosch
    Copyright   1997 Technische Universitaet Muenchen

instances for per - makes PER higher order
*)

PER = PER0 + (* instance for per *)

instance fun  :: (per,per)per   
{| (etac per_trans_fun 1) THEN (atac 1) THEN (etac per_sym_fun 1) |}

end
