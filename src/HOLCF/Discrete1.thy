(*  Title:      HOLCF/Discrete1.thy
    ID:         $Id$
    Author:     Tobias Nipkow

Discrete CPOs.
*)

Discrete1 = Discrete0 +

instance discr :: (type) po
  (less_discr_refl,less_discr_trans,less_discr_antisym)

end
