(* Title:     HOL/MiniML/Maybe.thy
   ID:        $Id$
   Author:    Wolfgang Naraschewski and Tobias Nipkow
   Copyright  1996 TU Muenchen

Universal error monad.
*)

Maybe = Main +

constdefs
  option_bind :: ['a option, 'a => 'b option] => 'b option
  "option_bind m f == case m of None => None | Some r => f r"

syntax "@option_bind" :: [pttrns,'a option,'b] => 'c ("(_ := _;//_)" 0)
translations "P := E; F" == "option_bind E (%P. F)"

end
