(*  Title:      Option.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994  TU Muenchen

Datatype 'a option
*)

Option = Arith +

datatype 'a option = None | Some 'a

constdefs

  the		:: "'a option => 'a"
 "the == %y. case y of None => arbitrary | Some x => x"

  option_map	:: "('a => 'b) => ('a option => 'b option)"
 "option_map == %f y. case y of None => None | Some x => Some (f x)"

consts

  o2s	   :: "'a option => 'a set"

primrec o2s option

 "o2s  None    = {}"
 "o2s (Some x) = {x}"

end
