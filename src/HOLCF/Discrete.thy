(*  Title:      HOLCF/Discrete.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Discrete CPOs.
*)

Discrete = Discrete1 +

instance discr :: (term)cpo   (discr_cpo)

constdefs
   undiscr :: ('a::term)discr => 'a
  "undiscr x == (case x of Discr y => y)"

end
