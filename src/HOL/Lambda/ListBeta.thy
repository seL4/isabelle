(*  Title:      HOL/Lambda/ListBeta.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TU Muenchen

Lifting beta-reduction to lists of terms, reducing exactly one element
*)

ListBeta = ListApplication + ListOrder +

syntax "=>" :: dB => dB => bool (infixl 50)
translations "rs => ss" == "(rs,ss) : step1 beta"

end
