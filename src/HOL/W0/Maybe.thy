(* Title:     HOL/W0/Maybe.thy
   ID:        $Id$
   Author:    Dieter Nazareth and Tobias Nipkow
   Copyright  1995 TU Muenchen

Universal error monad.
*)

Maybe = List +

datatype 'a maybe =  Ok 'a | Fail

constdefs
  bind :: ['a maybe, 'a => 'b maybe] => 'b maybe (infixl 60)
  "m bind f == case m of Ok r => f r | Fail => Fail"

syntax "@bind" :: [pttrns,'a maybe,'b] => 'c ("(_ := _;//_)" 0)
translations "P := E; F" == "E bind (%P.F)"

end
