(*  Title:      Option.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994  TU Muenchen

Datatype 'a option
*)

Option = Datatype +

datatype 'a option = None | Some 'a

consts
  the :: "'a option => 'a"
  o2s :: "'a option => 'a set"

primrec
 "the (Some x) = x"

primrec
 "o2s  None    = {}"
 "o2s (Some x) = {x}"

constdefs
  option_map	:: "('a => 'b) => ('a option => 'b option)"
 "option_map == %f y. case y of None => None | Some x => Some (f x)"

end
