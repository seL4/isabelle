(*  Title:      HOLCF/Discrete0.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1997 TUM

Proves that 'a discr is a po
*)

goalw thy [less_discr_def] "less (x::('a::term)discr) x";
br refl 1;
qed "less_discr_refl";

goalw thy [less_discr_def]
  "!!x. [| less (x::('a::term)discr) y; less y z |] ==> less x z";
be trans 1;
ba 1;
qed "less_discr_trans";

goalw thy [less_discr_def]
  "!!x. [| less (x::('a::term)discr) y; less y x |] ==> x=y";
ba 1;
qed "less_discr_antisym";
