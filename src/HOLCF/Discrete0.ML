(*  Title:      HOLCF/Discrete0.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Proves that 'a discr is a po
*)

Goalw [less_discr_def] "(x::('a::term)discr) << x";
by (rtac refl 1);
qed "less_discr_refl";

Goalw [less_discr_def]
  "!!x. [| (x::('a::term)discr) << y; y << z |] ==> x <<  z";
by (etac trans 1);
by (assume_tac 1);
qed "less_discr_trans";

Goalw [less_discr_def]
  "!!x. [| (x::('a::term)discr) << y; y << x |] ==> x=y";
by (assume_tac 1);
qed "less_discr_antisym";
