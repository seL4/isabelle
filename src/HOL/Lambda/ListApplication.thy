(*  Title:      HOL/Lambda/ListApplication.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TU Muenchen

Application of a term to a list of terms
*)

ListApplication = Lambda +

syntax "$$" :: dB => dB list => dB (infixl 150)
translations "t $$ ts" == "foldl op$ t ts"

end
