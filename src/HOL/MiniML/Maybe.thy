(* Title:     HOL/MiniML/Maybe.thy
   ID:        $Id$
   Author:    Dieter Nazareth and Tobias Nipkow
   Copyright  1995 TU Muenchen

Universal error monad.
*)

Maybe = List +

datatype 'a maybe =  Ok 'a | Fail

consts bind :: ['a maybe, 'a => 'b maybe] => 'b maybe (infixl 60)

defs
  bind_def "m bind f == case m of Ok r => f r | Fail => Fail"

end
