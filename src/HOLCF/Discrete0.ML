(*  Title:      HOLCF/Discrete0.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1997 TUM

Proves that 'a discr is a po
*)

goalw thy [less_discr_def] "less (x::('a::term)discr) x";
by (rtac refl 1);
qed "less_discr_refl";

goalw thy [less_discr_def]
  "!!x. [| less (x::('a::term)discr) y; less y z |] ==> less x z";
by (etac trans 1);
by (assume_tac 1);
qed "less_discr_trans";

goalw thy [less_discr_def]
  "!!x. [| less (x::('a::term)discr) y; less y x |] ==> x=y";
by (assume_tac 1);
qed "less_discr_antisym";
